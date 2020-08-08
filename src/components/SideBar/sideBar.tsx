import React from 'react'
import Menu from '../Menu'
import styles from  './sideBar.module.css';
import { MenuItem } from '../../models'

interface SideBarProps {
    headerContent?: any
    menu: MenuItem[]
    selectedRouteKey: any
    footerContent?: any
}

export default function SideBar(props: SideBarProps) {
    return (
        <div className={styles.sideBarContainer}>
            <div className={styles.sideBarHeader}>{props.headerContent}</div>
            <Menu
                selectedRouteKey={props.selectedRouteKey}
                itemList={props.menu}
            />
            <div className={styles.sideBarFooter}>{props.footerContent}</div>
        </div>
    )
}
