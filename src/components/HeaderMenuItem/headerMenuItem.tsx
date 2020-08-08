import React from 'react'
import styles from  './headerMenuItem.module.css';
import cn from 'classnames'
import Icon from '../../icons'

interface MenuItemProps {
    label?: string
    onClick: (routeKey?: string) => void
    iconComp?: any
    iconName?: string
    iconCompStyle? : React.CSSProperties;   
    style?: React.CSSProperties
}

export default function MenuItem(props: MenuItemProps) {
    var iconComp = props.iconComp ? (
        props.iconComp
    ) : props.iconName ? (
        <Icon
            style={props.iconCompStyle}
            className={cn(
                styles.menuItemIcon
            )}
            name={props.iconName}
        />
    ) : null


    return (
        <div
            onClick={() => {
                props.onClick()
            }}
            style={props.style}
            className={styles.menuItem}
        >
            {iconComp && <div style={{ padding: '0px 5px' }}>{iconComp}</div>}
            {props.label && <div>{props.label}</div>}
        </div>
    )
}
