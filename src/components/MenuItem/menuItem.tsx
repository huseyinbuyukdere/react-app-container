import React from 'react'
import styles from  './menuItem.module.css';
import cn from 'classnames'
import Icon from '../../icons'

interface MenuItemProps {
    label: string
    onClick: (routeKey?: string) => void
    iconComp?: any
    iconName?: string
    iconCompStyle? : React.CSSProperties;
    rightIconComp?: any
    rightIconName?: string
    rightIconCompStyle? : React.CSSProperties;
    style?: React.CSSProperties
    isSelected: boolean
    isFlat? : boolean
}

export default function MenuItem(props: MenuItemProps) {
    var iconComp = props.iconComp ? (
        props.iconComp
    ) : props.iconName ? (
        <Icon
            style={props.iconCompStyle}
            className={cn(
                styles.menuItemIcon,
                props.isSelected && styles.menuItemIconSelected
            )}
            name={props.iconName}
        />
    ) : null

    var rightIconComp = props.rightIconComp ? (
        props.rightIconComp
    ) : props.rightIconName ? (
        <Icon
            style={props.rightIconCompStyle}
            className={cn(
                styles.menuItemIcon,
                props.isSelected && styles.menuItemIconSelected
            )}
            name={props.rightIconName}
        />
    ) : null

    return (
        <div
            onClick={() => {
                props.onClick()
            }}
            style={props.style}
            className={cn(styles.menuItem, props.isSelected && styles.selected)}
        >
            {iconComp && <div style={{ marginRight: '10px' }}>{iconComp}</div>}
            {!props.isFlat && <div>{props.label}</div>}
            {rightIconComp && (
                <div style={{ marginLeft: 'auto' }}>{rightIconComp}</div>
            )}
        </div>
    )
}
